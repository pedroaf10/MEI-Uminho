package com.gamehub.Services;

import com.gamehub.Model.JSON.MensagemJSON;
import com.gamehub.Model.JSON.NaoLidasJSON;
import com.gamehub.Model.Users.CaixaMensagens;
import com.gamehub.Model.Users.Gamer;
import com.gamehub.Model.Users.Mensagem;
import com.gamehub.Repositories.CaixaMensagensRepository;
import com.gamehub.Repositories.GamerRepository;
import com.gamehub.Repositories.MensagemRepository;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

@Service
public class MensagemService {

    @Autowired
    private CaixaMensagensRepository caixaMensagensRepository;
    @Autowired
    private MensagemRepository mensagemRepository;
    @Autowired
    private GamerRepository gamerRepository;


    /**
     * Obter todas as mensagens de uma caixa de mensagens
     * @param idCaixaMensagem id da caixa de mensagens
     * @return Lista das mensagens
     */
    public List<Mensagem> getAllMensagens(int idCaixaMensagem) {
        List<Mensagem> mensagens = new ArrayList<>();
        Optional<CaixaMensagens> res = caixaMensagensRepository.findById(idCaixaMensagem);
        if (res.isPresent()) {
            CaixaMensagens caixa = res.get();
            mensagens.addAll(caixa.getMensagens());
        }
        return mensagens;
    }

    /**
     * Adiiconar uma mensagem a uma caixa de mensagens
     * @param idCaixaMensagem id da caixa de mensagens
     * @param mensagem mensagem
     * @param idGamer id do gamer que escrever mensagem
     * @return true se for bem sucedido, false caso contrário
     */
    public boolean addMensagemCaixa(int idCaixaMensagem, MensagemJSON mensagem, int idGamer) {
        Optional<CaixaMensagens> res = caixaMensagensRepository.findById(idCaixaMensagem);
        Optional<Gamer> res2 = gamerRepository.findById(idGamer);

        if (res.isPresent() && res2.isPresent()) {
            CaixaMensagens caixa = res.get();
            Gamer gamer = res2.get();
            Mensagem m = new Mensagem(mensagem.getConteudo(), caixa, gamer);
            caixa.addMensagem(m);
            this.caixaMensagensRepository.save(caixa);
            return true;
        }
        return false;
    }

    /**
     * Obter as mensagens que trocou com um determinado amigo
     * @param id_gamer id do gamer
     * @param id_amigo id gamer do amigo
     * @return Lista de mensagens trocadas
     */
    public List<Mensagem> getMensagensByAmigoGamer(int id_gamer, int id_amigo) {

        List<Mensagem> res = null;

        Integer caixa_id = this.gamerRepository.getCaixaMensagemComAmigo(id_gamer, id_amigo);

        if (caixa_id != null) {
            this.mensagemRepository.setMensagensLidas(caixa_id, id_gamer);
            Optional<CaixaMensagens> c = caixaMensagensRepository.findById(caixa_id);
            if (c.isPresent()) {
                CaixaMensagens caixa = c.get();
                res = caixa.getMensagens();
            } else {
                res = new ArrayList<>();
            }
        } else {
            res = new ArrayList<>();
        }

        return res;
    }

    /**
     * Obter o número de mensagens com um determinado amigo
     * @param id_gamer id do gamer
     * @param id_amigo id gamer do amigo
     * @return Número de mensagens trocadas
     */
    public Integer get_num_caixa_mensagem(int id_gamer, int id_amigo) {
        return this.gamerRepository.getCaixaMensagemComAmigo(id_gamer, id_amigo);
    }


    /**
     * Obter lista de número de mensagens não lidas
     * @param id_gamer id do gamer
     * @return Lista que para cada amigo fornece o número de mensagens não lidas
     */
    public List<NaoLidasJSON> getNumMensagensNaoLidasAmigo(int id_gamer) {
        List<NaoLidasJSON> res = new ArrayList<>();

        List<Integer> ids_amigos = this.gamerRepository.getIdsAmigos(id_gamer);
        if (!ids_amigos.isEmpty()) {
            for (Integer id_amigo : ids_amigos) {
                Integer temp = this.mensagemRepository.getNumMensagensByAmigo(id_gamer, id_amigo).orElse(0);

                NaoLidasJSON nlj = new NaoLidasJSON(temp, id_amigo);
                res.add(nlj);
            }
        }

        return res;
    }
}
