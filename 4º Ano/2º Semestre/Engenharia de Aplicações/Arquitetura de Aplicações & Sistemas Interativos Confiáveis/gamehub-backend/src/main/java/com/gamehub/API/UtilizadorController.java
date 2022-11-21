package com.gamehub.API;

import com.gamehub.Model.JSON.*;
import com.gamehub.Model.Posts.Grupo;
import com.gamehub.Model.Posts.Jogo;
import com.gamehub.Model.Users.Gamer;
import com.gamehub.Model.Users.Mensagem;
import com.gamehub.Model.Users.Utilizador;
import com.gamehub.Services.*;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.web.bind.annotation.*;

import javax.websocket.server.PathParam;
import java.util.ArrayList;
import java.util.List;

@CrossOrigin
@RequestMapping("api/v1/utilizador")
@RestController
public class UtilizadorController {

    private final UtilizadorService utilizadorService;
    private final GamerService gamerService;
    private final MensagemService mensagemService;
    private final JogoService jogoService;
    private final PostsService postsService;


    @Autowired
    public UtilizadorController(UtilizadorService utilizadorService, GamerService gs, MensagemService ms, JogoService js, PostsService postsService) {
        this.utilizadorService = utilizadorService;
        this.gamerService = gs;
        this.mensagemService = ms;
        this.jogoService = js;
        this.postsService = postsService;
    }

    /**
     * Método para inserir um novo utilizador
     * @param utilizador utilizador a inserir
     * @return -1 se o email já existe, 0 se o username já existe ou 1 caso seja inserido com sucesso
     */
    @PostMapping
    public int insertUtilizador(@RequestBody Utilizador utilizador) {
        return utilizadorService.insertUtilizador(utilizador);
    }

    /**
     * Método que realiza o login de um utilizador
     * @param login classe com os valores usados para o login
     * @return o gamer correspondete à sessão iniciada
     */
    @RequestMapping("/login")
    @PostMapping
    public Gamer login(@RequestBody LoginJSON login) {
        return utilizadorService.realiza_login(login.getEmail(), login.getPassword());
    }

    /**
     *
     * @param gamer_id Identificador único do Gamer
     */
    @RequestMapping("/logout/{id}")
    @PostMapping
    public void logout(@PathVariable(value = "id") int gamer_id) {
        gamerService.realiza_logout(gamer_id);
    }

    /**
     * Método que retorna todos os utilizadores
     * @return Lista de todos os utilizadores
     */
    @GetMapping
    public List<Utilizador> getAllUtilizadores() {
        return utilizadorService.getAllUtilizadores();
    }

    /**
     * Método responsável por obter todos os gamers presentes na base de dados
     * @return Lista com todos os gamers da bas de dados
     */
    @RequestMapping("/getAllGamers")
    @GetMapping
    public List<Gamer> getAllGamers() {
        return gamerService.getAllGamers();
    }

    /**
     * Obter um utilizador a partir do seu ID
     * @param id id do utilizador
     * @return utilizador encontrado
     */
    @RequestMapping("/{id}")
    @GetMapping
    public @ResponseBody
    Utilizador getUtilizadorById(@PathVariable(value = "id") String id) {
        return utilizadorService.getUtilizadorById(Integer.parseInt(id));
    }

    /**
     * Método responsável por obter todos os jogos que um gamer não segue
     * @param gamer_id Identificador do gamer a verificar
     * @return Retorna a lista com os jogos que ele não segue
     */
    @RequestMapping("/jogosporseguir/{id}")
    @GetMapping
    public List<Jogo> getJogosPorSeguir(@PathVariable(value = "id") int gamer_id) {
        return jogoService.getJogosPorSeguir(gamer_id);
    }

    /**
     * Método responsável por obter o perfil de um gamer
     * @param idGamer Identificador único do Gamer
     * @return Informação de um Gamer
     */
    @RequestMapping("/getPerfil/{id}")
    @GetMapping
    public Gamer getPerfil(@PathVariable(value = "id") int idGamer) {
        return gamerService.getGamerById(idGamer);
    }

    /**
     * Método responsável por obter o perfil de um determinado gamer
     * @param idGamer Identificador único do Gamer que visualizará o perfil
     * @param id_amigo Identificador único do Gamer amigo a que se irá visualizar o perfil
     * @return Retorna uma classe especial com a informação do perfil do gamer (identificador id_gamer)
     *          + uma informação a dizer se esse gamer pode ser avaliado por gamer com o identificador id
     */
    @RequestMapping("/getPerfilAmigo/{id}/{id_amigo}")
    @GetMapping
    public PerfilAmigosJSON getPerfilAmigo(@PathVariable(value = "id") int idGamer, @PathVariable(value = "id_amigo") int id_amigo) {
        return gamerService.getPerfilGamer(idGamer, id_amigo);
    }

    /**
     * Método responsável por obter o perfil de um determinado gamer
     * @param id_origem Identificador único do Gamer que visualizará o perfil
     * @param id_gamer Identificador único do Gamer amigo a que se irá visualizar o perfil
     * @return Retorna uma classe especial com a informação do perfil do gamer (identificador id_gamer)
     *          + uma informação a dizer se esse gamer pode ser avaliado por gamer com o identificador id
     */
    @RequestMapping("/getPerfilGamer/{id}/{id_gamer}")
    @GetMapping
    public PerfilAmigosJSON getPerfilGamer(@PathVariable(value = "id") int id_origem, @PathVariable(value = "id_gamer") int id_gamer) {
        return gamerService.getPerfilGamer(id_origem, id_gamer);
    }

    /**
     * Obter um grupo dado o seu id
     * @param idGrupo id do grupo
     * @return o grupo encontrado
     */
    @RequestMapping("/getGrupo/{id}")
    @GetMapping
    public Grupo getGrupoGamer(@PathVariable(value = "id") int idGrupo) {
        return postsService.get_grupo_by_id(idGrupo);
    }

    /**
     * Obtém o grupo de um gamer
     * @param idGamer id do gamer
     * @return
     */
    @RequestMapping("/getGrupoID/{id}")
    @GetMapping
    public int getGrupoIDGamer(@PathVariable(value = "id") int idGamer) {
        Grupo g = gamerService.getGamerById(idGamer).getGrupo();
        return (g != null) ? g.getId() : -1;
    }

    /**
     * Método responsável por atualizar um determiando nome de um Gamer
     * @param idGamer Identificador único do Gamer
     * @param nome Novo nome a inserir
     * @return retorna um booleano com a veracidade da concretização do método
     */
    @RequestMapping("/setnomegamer/{id}/{nome}")
    @PostMapping
    public boolean setNomeGamer(@PathVariable(value = "id") int idGamer, @PathVariable(value = "nome") String nome) {
        return gamerService.updateNomeGamer(idGamer, nome);
    }

    /**
     * Método responsável por atualizar o avatar de um gamer
     * @param idGamer Identificador único do Gamer
     * @param link Novo link que redireciona para o novo avatar
     * @return retorna um booleano com a veracidade da concretização do método
     */
    @RequestMapping("/setavatargamer/{id}")
    @PostMapping
    public boolean setAvatarGamer(@PathVariable(value = "id") int idGamer, @RequestParam(defaultValue = "link") String link) {
        return gamerService.updateAvatarGamer(idGamer, link);
    }

    /**
     * Método responsável por defenir o avatar padrão para o seu username atual
     * @param idGamer Identificador único do Gamer
     * @return retorna um booleano com a veracidade da concretização do método
     */
    @RequestMapping("/resetavatargamer/{id}")
    @PostMapping
    public boolean resetAvatarGamer(@PathVariable(value = "id") int idGamer) {
        return gamerService.resetAvatar(idGamer);
    }

    /**
     * Adiiconar uma mensagem a uma caixa de mensagens
     * @param idCaixa id da caixa de mensagens
     * @param mensagem conteudo da mensagem
     * @param id_gamer id do gamer que escrever mensagem
     * @return true se for bem sucedido, false caso contrário
     */
    @RequestMapping("/addmensagemGrupo/{id}")
    @PostMapping
    public boolean addMensagem(@PathVariable(value = "id") int idCaixa, @PathParam(value = "id_gamer") int id_gamer, @RequestBody MensagemJSON mensagem) {
        return mensagemService.addMensagemCaixa(idCaixa, mensagem, id_gamer);
    }

    /**
     * Obter todas as mensagens de uma caixa de mensagens
     * @param idCaixa id da caixa de mensagens
     * @return Lista das mensagens
     */
    @RequestMapping("/getmensagenscaixa/{id}")
    @GetMapping
    public List<Mensagem> getMensagensCaixa(@PathVariable(value = "id") int idCaixa) {
        return mensagemService.getAllMensagens(idCaixa);
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
    @RequestMapping("/adicionaramigo/{id}/{nome}")
    @PostMapping
    public int adicionarAmigo(@PathVariable(value = "id") int idGamer, @PathVariable(value = "nome") String nomeAmigo) {
        return gamerService.adicionarAmigo(idGamer, nomeAmigo);
    }

    /**
     * Método responsável por remover uma determinada amizade de um gamer
     * @param idGamer Identificador único do Gamer
     * @param id_amigo Identicador do gamer a deixar de ser amigo
     * @return retorna um booleano com a veracidade da concretização do método
     */
    @RequestMapping("/removeramigo/{id}")
    @PostMapping
    public boolean removerAmigo(@PathVariable(value = "id") int idGamer, @RequestParam(defaultValue = "id_amigo") int id_amigo) {
        return gamerService.removerAmigo(idGamer, id_amigo);
    }

    /**
     * Obtém os gamer do mesmo grupo de um determinado gamer
     * @param idGamer id do gamer
     * @return informações necessárias para mostrar a informação dos gamers
     */
    @RequestMapping("/getgamersdomesmogrupo/{id}")
    @GetMapping
    public List<NomeAvatarIdJSON> getGamersDoMesmoGrupo(@PathVariable(value = "id") int idGamer) {
        Integer grupoID = gamerService.getGrupoGamer(idGamer);
        List<Gamer> gamers = postsService.getPessoasGrupo(grupoID);

        List<NomeAvatarIdJSON> res = new ArrayList<>();
        for (Gamer g : gamers) {
            if (g.getId() != idGamer) {
                NomeAvatarIdJSON temp = new NomeAvatarIdJSON(g.getId(), g.getAvatar(), g.getNome());
                res.add(temp);
            }
        }

        return res;
    }

    /**
     * Método que obtem a lista dos jogos seguidos por um gamer
     * @param id_gamer Identificador único do Gamer
     * @return Lista com os jogos que o gamer segue
     */
    @RequestMapping("/getListaJogosSeguir/{id}")
    @GetMapping
    public List<Jogo> get_lista_jogos_a_seguir(@PathVariable(value = "id") int id_gamer) {
        return gamerService.get_lista_jogos_a_seguir(id_gamer);
    }

    /**
     * Juntar a um grupo
     * @param id_gamer id do gamer
     * @param id_post_grupo id do post grupo
     * @return boleano com a resultado da resolução do método
     */
    @RequestMapping("/juntarGrupo/{id}")
    @PostMapping
    public boolean juntar_grupo(@PathVariable(value = "id") int id_gamer, @RequestParam(defaultValue = "idGrupo") int id_post_grupo) {
        boolean sucesso = false;
        boolean esta_grupo = gamerService.is_gamer_in_grupo(id_gamer);

        if (esta_grupo) {
            gamerService.sairGrupo(id_gamer);
        }


        Grupo g = postsService.get_Grupo_by_post(id_post_grupo);

        if (g != null) {
            if (g.is_full()) {
                g = null;
            }
        }

        if (g != null) {
            gamerService.set_gamer_to_grupo(id_gamer, g);
            postsService.add_participante_grupo(gamerService.getGamerById(id_gamer), g.getId());
            sucesso = true;
        }


        return sucesso;
    }

    /**
     * Retirar um gamer do seu grupo
     * @param id_gamer id do gamer
     * @return o suecesso da operação
     */
    @RequestMapping("/sairGrupo/{id}")
    @PostMapping
    public boolean sair_grupo(@PathVariable(value = "id") int id_gamer) {
        boolean sucesso = false;
        int id_grupo = this.gamerService.sairGrupo(id_gamer);
        if (id_grupo > 0) {
            this.postsService.apagar_grupo_se_vazio(id_grupo);
            sucesso = true;
        }
        return sucesso;
    }

    /**
     * Método que avalia um gamer
     * @param avaliador Identificador do gamer avaliador
     * @param avaliado Identificador do gamer que irá ser avalidado
     * @param classificacao Valor que foi atribuido à avaliação
     */
    @RequestMapping("/avaliaGamer/{avaliador}/{avaliado}")
    @PostMapping
    public void avalia_gamer(@PathVariable(value = "avaliador") int avaliador, @PathVariable(value = "avaliado") int avaliado, @RequestParam(defaultValue = "classificacao") int classificacao) {
        gamerService.avalia_gamer(avaliador, avaliado, classificacao);
    }

    /**
     * Obter as mensagens que trocou com um determinado amigo
     * @param id_gamer id do gamer
     * @param id_amigo id gamer do amigo
     * @return Lista de mensagens trocadas
     */
    @RequestMapping("/getMensagensComAmigo/{id}")
    @GetMapping
    public List<Mensagem> getCaixaMensagemComAmigo(@PathVariable(value = "id") int id_gamer, @RequestParam(defaultValue = "id_amigo") int id_amigo) {
        return this.mensagemService.getMensagensByAmigoGamer(id_gamer, id_amigo);
    }

    /**
     * Enviar uma mensagem a um determinado amigo
     * @param id_amigo id do amigo a quem se enviou a mensagem
     * @param mensagem mensagem
     * @param id_gamer id do gamer que escrever mensagem
     * @return true se for bem sucedido, false caso contrário
     */
    @RequestMapping("/addmensagemAmigo/{id}")
    @PostMapping
    public boolean addMensagemAmigo(@PathVariable(value = "id") int id_gamer, @RequestParam(defaultValue = "id_amigo") int id_amigo, @RequestBody MensagemJSON mensagem) {
        int id_Caixa = this.mensagemService.get_num_caixa_mensagem(id_gamer, id_amigo);
        return mensagemService.addMensagemCaixa(id_Caixa, mensagem, id_gamer);
    }

    /**
     * Método responsável por permitir a um gamer seguir um novo jogo
     * @param id_gamer Identificador único do Gamer
     * @param jogos Lista com todos os jogos que o gamer deve seguir
     * @return retorna um booleano com a veracidade da concretização do método
     */
    @RequestMapping("/addJogoSeguir/{id}")
    @PostMapping
    public boolean addJogoSeguir(@PathVariable(value = "id") int id_gamer, @RequestBody ListaJogosJSON jogos) {
        return gamerService.addJogoSerguir(id_gamer, jogos.getJogos());
    }

    /**
     * Método que permite a um gamer deixar de seguir um jogo
     * @param id_gamer Identificador único do Gamer
     * @param id_jogo Identificador do jogo a deixar de seguir
     * @return retorna um booleano com a veracidade da concretização do método
     */
    @RequestMapping("/stopJogoSeguir/{id}")
    @PostMapping
    public boolean stopJogoSeguir(@PathVariable(value = "id") int id_gamer, @RequestParam(defaultValue = "id_jogo") int id_jogo) {
        return gamerService.stopJogoSerguir(id_gamer, id_jogo);
    }

    /**
     * Obter lista de número de mensagens não lidas
     * @param id_gamer id do gamer
     * @return Lista que para cada amigo fornece o número de mensagens não lidas
     */
    @RequestMapping("/getNumMensagensNaoLidasAmigo/{id}")
    @GetMapping
    public List<NaoLidasJSON> getNumMensagensNaoLidasAmigo(@PathVariable(value = "id") int id_gamer) {
        return this.mensagemService.getNumMensagensNaoLidasAmigo(id_gamer);
    }

    /**
     * Método responsável por banir (eleiminar toda a informação) um gamer
     * @param id_gamer Identificador único do Gamer
     */
    @RequestMapping("/banirGamer/{id}")
    @PostMapping
    @Transactional
    public boolean banirGamer(@PathVariable(value = "id") int id_gamer) {
        boolean res = this.sair_grupo(id_gamer);
        if(res)
            this.gamerService.banirGamer(id_gamer);
        return res;
    }
}
