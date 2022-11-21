package com.gamehub.Services;

import com.gamehub.Model.JSON.PerfilAmigosJSON;
import com.gamehub.Model.Posts.Grupo;
import com.gamehub.Model.Posts.Jogo;
import com.gamehub.Model.Posts.PostGrupo;
import com.gamehub.Model.Posts.PostMultimedia;
import com.gamehub.Model.Users.Avatar;
import com.gamehub.Model.Users.CaixaMensagens;
import com.gamehub.Model.Users.Gamer;
import com.gamehub.Repositories.*;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

@Service
public class GamerService {

    @Autowired
    private GamerRepository gamerRepository;
    @Autowired
    private AvatarRepository avatarRepository;
    @Autowired
    private JogoRepository jogoRepository;
    @Autowired
    private CaixaMensagensRepository caixaMensagensRepository;
    @Autowired
    private MensagemRepository mensagemRepository;
    @Autowired
    private UtilizadorRepository utilizadorRepository;

    /**
     * Método responsável por inserir um gamer na base de dados
     * @param gamer Gamer a inserir na base de dados
     */
    public void insertGamer(Gamer gamer) {
        gamerRepository.save(gamer);
    }

    /**
     * Método responsável por obter todos os gamers presentes na base de dados
     * @return Lista com todos os gamers da bas de dados
     */
    public List<Gamer> getAllGamers() {
        List<Gamer> gamers = new ArrayList<>();
        gamerRepository.findAll().forEach(gamers::add);
        return gamers;
    }

    /**
     * Método responsável por denvolver um gamer com um determinado identificador único
     * @param id Identificador único do Gamer
     * @return Gamer com um determinado identificador
     */
    public Gamer getGamerById(int id) {
        Optional<Gamer> res = gamerRepository.findById(id);
        return res.orElse(null);
    }

    /**
     * Método responsável por atualizar um determiando nome de um Gamer
     * @param id Identificador único do Gamer
     * @param nome Novo nome a inserir
     * @return retorna um booleano com a veracidade da concretização do método
     */
    public boolean updateNomeGamer(int id, String nome) {
        Optional<Gamer> gamerNome = Optional.ofNullable(gamerRepository.findByNome(nome));

        if (gamerNome.isEmpty()) {
            Optional<Gamer> res = gamerRepository.findById(id);
            if (res.isPresent()) {
                Gamer gamer = res.get();
                gamer.setNome(nome);
                gamerRepository.save(gamer);
                return true;
            }
        }

        return false;
    }

    /**
     * Método responsável por atualizar o avatar de um gamer
     * @param id Identificador único do Gamer
     * @param link Novo link que redireciona para o novo avatar
     * @return retorna um booleano com a veracidade da concretização do método
     */
    public boolean updateAvatarGamer(int id, String link) {
        Optional<Gamer> res = gamerRepository.findById(id);
        if (res.isPresent()) {
            Gamer gamer = res.get();
            Avatar avatar = gamer.getAvatar();
            avatar.setLink(link);
            this.avatarRepository.save(avatar);
            return true;
        }
        return false;
    }

    /**
     * Método responsável por defenir o avatar padrão para o seu username atual
     * @param id Identificador único do Gamer
     * @return retorna um booleano com a veracidade da concretização do método
     */
    public boolean resetAvatar(int id) {
        Optional<Gamer> res = gamerRepository.findById(id);
        if (res.isPresent()) {
            Gamer gamer = res.get();
            Avatar avatar = gamer.getAvatar();
            String link = "https://api.multiavatar.com/" + gamer.getNome() + ".png";
            avatar.setLink(link);
            this.avatarRepository.save(avatar);
            return true;
        }
        return false;
    }

    /**
     * Método resposável por inserir novos avatares na base de dados
     * @param avatar Novo avatar a inserir
     */
    public void insertAvatar(Avatar avatar) {
        avatarRepository.save(avatar);
    }

    /**
     * Método responsável por obter todos os avatares existentes na base de dados
     * @return Lista com todos os avatares existentes na base de dados
     */
    public List<Avatar> getAllAvatares() {
        List<Avatar> avatares = new ArrayList<>();
        avatarRepository.findAll().forEach(avatares::add);
        return avatares;
    }

    /**
     * Método responsável por obter um determinado avatar
     * @param id Identificador unico do avatar
     * @return O avatar encontrado na base de dados
     */
    public Avatar getAvatarById(int id) {
        Optional<Avatar> res = avatarRepository.findById(id);
        return res.orElse(null);
    }

    /**
     * Método responsável por adicionar um amigo num Gamer
     * @param idGamer Identificador único do Gamer
     * @param nomeAmigo Identificador único do novo amigo
     * @return Retorna:
     *                  1 -> Se a operação foi realizado com sucesso
     *                  2 -> Se um dos gamers não existir
     *                  3 -> Se já são amigos
     */
    public int adicionarAmigo(int idGamer, String nomeAmigo) {

        CaixaMensagens caixa = new CaixaMensagens();

        Optional<Gamer> gamer = gamerRepository.findById(idGamer);
        Optional<Gamer> amigo = Optional.ofNullable(gamerRepository.findByNome(nomeAmigo));

        int res = 2;
        if (gamer.isPresent() && amigo.isPresent()) {
            Gamer g = gamer.get();
            Gamer g2 = amigo.get();

            if (!g.getAmigos().contains(g2) && !g2.getAmigos().contains(g)) {

                g.addAmigo(g2);
                g2.addAmigo(g);

                g.addCaixaMensagem(caixa);
                g2.addCaixaMensagem(caixa);

                gamerRepository.save(g);
                gamerRepository.save(g2);
                res = 1;
            } else res = 3;
        }
        return res;
    }

    /**
     * Método que obtem o identificador de um grupo a que um agmer pertence
     * @param idGamer Identificador único do Gamer
     * @return Identificador do grupo
     */
    public Integer getGrupoGamer(int idGamer) {
        Integer res = null;
        Optional<Gamer> gamer = gamerRepository.findById(idGamer);
        if (gamer.isPresent()) {
            Gamer g = gamer.get();
            Grupo grupo = g.getGrupo();
            res = grupo.getId();
        }
        return res;
    }

    /**
     * Método que obtem a lista dos jogos seguidos por um gamer
     * @param id_gamer Identificador único do Gamer
     * @return Lista com os jogos que o gamer segue
     */
    public List<Jogo> get_lista_jogos_a_seguir(int id_gamer) {
        Gamer g = this.getGamerById(id_gamer);
        return g.getJogos();
    }

    /**
     * Método que verifica se um gamer já se encontra num grupo
     * @param id_gamer Identificador único do Gamer
     * @return retorna um booleano com a veracidade da concretização do método
     */
    public boolean is_gamer_in_grupo(int id_gamer) {
        Gamer g = this.getGamerById(id_gamer);
        return g.getGrupo() != null;
    }

    /**
     * Método responsável por adicionar um gamer a um determinado grupo
     * @param id_gamer Identificador único do Gamer
     * @param grupo Grupo em que o gamer tem de ser adicionado
     */
    public void set_gamer_to_grupo(int id_gamer, Grupo grupo) {
        Gamer g = this.getGamerById(id_gamer);

        List<Gamer> membros_grupo = grupo.getGamers();

        for (Gamer gamer : membros_grupo) {
            this.gamerRepository.addAvaliacaoPossivel(gamer.getId(), id_gamer);
            this.gamerRepository.addAvaliacaoPossivel(id_gamer, gamer.getId());
        }

        g.setGrupo(grupo);


        this.gamerRepository.save(g);
    }

    /**
     * Método que avalia um gamer
     * @param avaliador Identificador do gamer avaliador
     * @param avaliado Identificador do gamer que irá ser avalidado
     * @param classificacao Valor que foi atribuido à avaliação
     */
    public void avalia_gamer(int avaliador, int avaliado, int classificacao) {
        Gamer gamerAvaliado = this.getGamerById(avaliado);

        gamerRepository.deleteFromPossiveisAvaliacoes(avaliador, avaliado);

        gamerAvaliado.avalia(classificacao);
        this.gamerRepository.save(gamerAvaliado);
    }

    /**
     *
     * @param gamer_id Identificador único do Gamer
     */
    public void realiza_logout(int gamer_id) {
        Gamer g = this.getGamerById(gamer_id);
        g.setEstado("Offline");
        this.gamerRepository.save(g);
    }

    /**
     * Método responsável por permitir a um gamer seguir um novo jogo
     * @param id_gamer Identificador único do Gamer
     * @param jogos Lista com todos os jogos que o gamer deve seguir
     * @return retorna um booleano com a veracidade da concretização do método
     */
    public boolean addJogoSerguir(int id_gamer, List<Integer> jogos) {
        boolean res = false;
        Optional<Gamer> gamer = gamerRepository.findById(id_gamer);
        if (gamer.isPresent()) {
            Gamer g = gamer.get();
            List<Jogo> jogosLista = new ArrayList<>();

            for (int id_jogo : jogos) {
                Optional<Jogo> jogoOptional = this.jogoRepository.findById(id_jogo);
                if (jogoOptional.isPresent()) {
                    Jogo jogo = jogoOptional.get();
                    if (!g.getJogos().contains(jogo))
                        jogosLista.add(jogo);
                }
            }
            res = g.addJogos(jogosLista);
            this.gamerRepository.save(g);
        }
        return res;
    }

    /**
     * Método que permite a um gamer deixar de seguir um jogo
     * @param id_gamer Identificador único do Gamer
     * @param id_jogo Identificador do jogo a deixar de seguir
     * @return retorna um booleano com a veracidade da concretização do método
     */
    public boolean stopJogoSerguir(int id_gamer, int id_jogo) {
        boolean res = false;
        Optional<Gamer> gamer = gamerRepository.findById(id_gamer);
        if (gamer.isPresent()) {
            Gamer g = gamer.get();

            Optional<Jogo> jogoOptional = this.jogoRepository.findById(id_jogo);
            if (jogoOptional.isPresent()) {
                Jogo jogo = jogoOptional.get();
                res = g.removeJogo(jogo);
                this.gamerRepository.save(g);
            }
        }
        return res;
    }

    /**
     * Método responsável por remover um gamer de um detrminado grupo.
     * @param id_gamer Identificador único do Gamer
     * @return Identificador do grupo se existir. Caso contrário -1
     */
    public int sairGrupo(int id_gamer) {
        int id_grupo = -1;
        Optional<Gamer> gamer = gamerRepository.findById(id_gamer);
        if (gamer.isPresent()) {
            Gamer g = gamer.get();
            if (g.getGrupo() != null) {
                id_grupo = g.getGrupo().getId();
                g.setGrupo(null);

                this.gamerRepository.save(g);
            }
        }

        return id_grupo;
    }

    /**
     * Método responsável por remover uma determinada amizade de um gamer
     * @param idGamer Identificador único do Gamer
     * @param id_amigo Identicador do gamer a deixar de ser amigo
     * @return retorna um booleano com a veracidade da concretização do método
     */
    public boolean removerAmigo(int idGamer, int id_amigo) {
        boolean res = false;
        Optional<Gamer> gamer = gamerRepository.findById(idGamer);
        if (gamer.isPresent()) {
            Gamer g = gamer.get();
            Optional<Gamer> amigo = gamerRepository.findById(id_amigo);
            if (amigo.isPresent()) {
                Gamer g2 = amigo.get();
                res = g.remove_amigo(g2);
                if (res) {
                    res = g2.remove_amigo(g);
                    if (res) {

                        int id_caixa = this.gamerRepository.getCaixaMensagemComAmigo(idGamer, id_amigo);

                        CaixaMensagens caixa = this.caixaMensagensRepository.findById(id_caixa).orElse(null);

                        if (caixa != null) {
                            g.remove_caixa_mensagem(caixa);
                            g2.remove_caixa_mensagem(caixa);
                            this.caixaMensagensRepository.delete(caixa);
                        }
                        this.gamerRepository.save(g);
                        this.gamerRepository.save(g2);
                    }
                }
            }
        }
        return res;
    }

    /**
     * Método responsável por obter o perfil de um determinado gamer
     * @param id Identificador único do Gamer que visualizará o perfil
     * @param id_gamer Identificador único do Gamer amigo a que se irá visualizar o perfil
     * @return Retorna uma classe especial com a informação do perfil do gamer (identificador id_gamer)
     *          + uma informação a dizer se esse gamer pode ser avaliado por gamer com o identificador id
     */
    public PerfilAmigosJSON getPerfilGamer(int id, int id_gamer) {
        Gamer amigo = gamerRepository.findById(id_gamer).orElse(null);
        boolean b = false;

        if (amigo != null) {
            int podeAvaliar = gamerRepository.podeAvaliar(id, id_gamer).intValue();
            if (podeAvaliar == 1) {
                b = true;
            }
        }
        return (amigo != null) ? new PerfilAmigosJSON(amigo, b) : null;
    }

    /**
     * Método responsável por banir (eleiminar toda a informação) um gamer
     * @param id_gamer Identificador único do Gamer
     */
    public void banirGamer(int id_gamer) {

        Gamer gamer = gamerRepository.findById(id_gamer).orElse(null);
        int id_avatar = 0;
        if (gamer != null) {
            List<PostGrupo> pgs = gamer.getPublicacoes_grupo();
            for (PostGrupo pg : pgs) {
                Gamer gamehub = gamerRepository.findById(1).orElse(null);
                pg.setGamer(gamehub);
            }

            id_avatar = gamer.getAvatar().getId();
            List<PostMultimedia> pms = gamer.getPublicacoes_media();
            for (PostMultimedia pm : pms) {
                Integer id = pm.getId();
                gamerRepository.deleteDislikesPost(id);
                gamerRepository.deleteLikesPost(id);
            }
        }


        mensagemRepository.deleteMensagensGamer(id_gamer);
        List<Integer> ids = gamerRepository.getIdsAmigos(id_gamer);
        for (Integer id : ids) {
            int id_caixa = gamerRepository.getCaixaMensagemComAmigo(id_gamer, id);
            mensagemRepository.deleteConversas(id_caixa);
            mensagemRepository.deleteMensagensCaixa(id_caixa);
            mensagemRepository.deleteMensagensRemetente(id_gamer);
            mensagemRepository.deleteCaixasMensagens(id_caixa);
        }


        gamerRepository.deleteAmigos(id_gamer);
        mensagemRepository.deleteConversasGamer(id_gamer);
        gamerRepository.deletePossiveisAvaliacoesGamer(id_gamer);
        gamerRepository.deleteRecompensasGamer(id_gamer);
        gamerRepository.deleteJogosGamer(id_gamer);

        gamerRepository.deleteDislikesGamer(id_gamer);
        gamerRepository.deleteLikesGamer(id_gamer);

        gamerRepository.deletePostMultimediaTags(id_gamer);

        gamerRepository.deletePostMultimediaGamer(id_gamer);

        utilizadorRepository.deleteUtilizadorGamer(id_gamer);
        gamerRepository.deleteGamer(id_gamer);

        avatarRepository.deleteAvatar(id_avatar);

    }
}
