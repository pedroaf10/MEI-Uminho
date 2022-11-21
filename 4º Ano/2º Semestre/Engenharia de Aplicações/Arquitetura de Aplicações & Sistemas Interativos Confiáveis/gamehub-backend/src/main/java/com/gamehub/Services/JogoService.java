package com.gamehub.Services;

import com.gamehub.Model.JSON.JogosPopularesJSON;
import com.gamehub.Model.Posts.Jogo;
import com.gamehub.Repositories.JogoRepository;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

@Service
public class JogoService {

    @Autowired
    private JogoRepository jogoRepository;


    /**
     * Método responsável por inserir um novo jogo na base de dados
     * @param jogo Jogo a ser guaradado na base de dados
     */
    public void insertJogo(Jogo jogo) {
        jogoRepository.save(jogo);
    }

    /**
     * Método responsável por obter todos os jogos da base de dados
     * @return Lista com todos os jogos na base de dados
     */
    public List<Jogo> getAllJogos() {
        List<Jogo> jogos = new ArrayList<>();
        jogoRepository.findAll().forEach(jogos::add);
        return jogos;
    }

    /**
     * Método responsável por obter um jogo, consoante um determinado identificador
     * @param id Identificado do jogo
     * @return a classe jogo encontrada. Null se não existir
     */
    public Jogo getJogoById(int id) {
        Optional<Jogo> res = jogoRepository.findById(id);
        return res.orElse(null);
    }

    /**
     * Método responsável por obter os jogos mais populares. Ou seja os jogos mais seguidos
     * @param limit Define o TOP-limit a encontrar. Por exemplo, se limit=4 será o TOP-4.
     * @return Retorna a lista com os jogos mais seguidos + a informação de quantos seguidores tem cada jogo.
     */
    public List<JogosPopularesJSON> getJogosPopulares(int limit) {
        List<JogosPopularesJSON> res = new ArrayList<>();
        List<Jogo> temp = jogoRepository.findMostPopular(limit);

        for (Jogo j : temp) {
            int seguidores = this.jogoRepository.getNumSeguidores(j.getId());
            JogosPopularesJSON jp = new JogosPopularesJSON(j, seguidores);
            res.add(jp);
        }

        return res;
    }

    /**
     * Método responsável por obter todos os jogos que um gamer não segue
     * @param gamer_id Identificador do gamer a verificar
     * @return Retorna a lista com os jogos que ele não segue
     */
    public List<Jogo> getJogosPorSeguir(int gamer_id) {
        return jogoRepository.getJogosPorSeguir(gamer_id);
    }

    /**
     * Método responsável por encontrar o banner de um determinado nome de jogo
     * @param jogo Nome do jogo
     * @return Link com o endereço do banner
     */
    public String getLinkBannerJogo(String jogo) {
        return this.jogoRepository.getLinkBannerJogo(jogo);
    }
}
